import PfaffianDescent.VoisinPolynomialGenericSpreading
import AllCharacteristics.HomogeneousProjective
import AllCharacteristics.ProjectiveBaseChange
import PfaffianDescent.HomogeneousQuotientMap
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Ideal

/-!
# Homogeneous spreading of a generic fixed-curve ideal

A projective fixed curve is represented by a homogeneous ideal over the
configuration function field.  Its finite generators must retain homogeneous
degrees when spread to an affine coefficient ring.
-/

namespace PfaffianDescent

open MvPolynomial
open CategoryTheory
open AllCharacteristics.HomogeneousProjective

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- A homogeneous ideal in four variables over a field has a finite set of
homogeneous polynomial generators. -/
theorem homogeneousIdeal_exists_finite_homogeneous_generators
    {F : Type u} [Field F]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) :
    ∃ T : Finset (MvPolynomial (Fin 4) F),
      C.toIdeal = Ideal.span (T : Set (MvPolynomial (Fin 4) F)) ∧
        ∀ f ∈ T, ∃ n : ℕ, f.IsHomogeneous n := by
  classical
  obtain ⟨S, hS⟩ :=
    (Ideal.IsHomogeneous.iff_exists
      (homogeneousSubmodule (Fin 4) F) C.toIdeal).mp C.isHomogeneous
  let H : Set (MvPolynomial (Fin 4) F) := Subtype.val '' S
  have hfg : (Ideal.span H : Ideal (MvPolynomial (Fin 4) F)).FG := by
    rw [← hS]
    exact IsNoetherian.noetherian C.toIdeal
  obtain ⟨T₀, hT₀⟩ := hfg
  have hT₀subset : (T₀ : Set (MvPolynomial (Fin 4) F)) ⊆
      Submodule.span (MvPolynomial (Fin 4) F) H := by
    intro f hf
    have hmem : f ∈ Ideal.span H := by
      rw [← hT₀]
      exact Ideal.subset_span hf
    exact hmem
  obtain ⟨T, hTS, hTspan⟩ :=
    Submodule.subset_span_finite_of_subset_span hT₀subset
  refine ⟨T, ?_, ?_⟩
  · apply le_antisymm
    · rw [hS, ← hT₀]
      exact Ideal.span_le.mpr hTspan
    · rw [hS]
      exact Ideal.span_mono hTS
  · intro f hf
    obtain ⟨s, hs, rfl⟩ := hTS hf
    obtain ⟨n, hn⟩ := s.property
    exact ⟨n, hn⟩

/-- A homogeneous curve ideal over a fraction field has a homogeneous,
finitely generated model over the coefficient domain with exactly the given
generic ideal.  This is the graded algebraic input for a relative `Proj`
family; flatness and control of its divisor class are later geometric steps. -/
theorem exists_homogeneousIdeal_spread_of_fractionField
    {A : Type u} {F : Type v}
    [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) :
    ∃ J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A),
      J.toIdeal.FG ∧
        Ideal.map (MvPolynomial.map (algebraMap A F)) J.toIdeal = C.toIdeal := by
  classical
  obtain ⟨T, hCT, hThom⟩ :=
    homogeneousIdeal_exists_finite_homogeneous_generators C
  let ι := {f : MvPolynomial (Fin 4) F // f ∈ T}
  let f : ι → MvPolynomial (Fin 4) F := Subtype.val
  letI : Fintype ι := (Finset.finite_toSet T).fintype
  obtain ⟨d, hd, hclear⟩ :=
    exists_finite_polynomials_common_denominator_clear
      (A := A) (F := F) (Finset.univ : Finset ι) f
  let g : ι → MvPolynomial (Fin 4) A :=
    fun i => Classical.choose (hclear i (Finset.mem_univ i))
  have hg : ∀ i, MvPolynomial.map (algebraMap A F) (g i) =
      MvPolynomial.C (algebraMap A F d) * f i := by
    intro i
    exact Classical.choose_spec (hclear i (Finset.mem_univ i))
  have hghom : ∀ i, ∃ n : ℕ, (g i).IsHomogeneous n := by
    intro i
    obtain ⟨n, hn⟩ := hThom i.1 i.2
    exact ⟨n, polynomial_denominator_clear_isHomogeneous
      (f i) (g i) d n hn (hg i)⟩
  let J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A) :=
    ⟨Ideal.span (Set.range g), Ideal.homogeneous_span _ _ (by
      intro x hx
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨n, hn⟩ := hghom i
      exact SetLike.isHomogeneousElem_coe ⟨g i, hn⟩)⟩
  refine ⟨J, ?_, ?_⟩
  · exact Submodule.fg_span (Set.finite_range g)
  · change Ideal.map (MvPolynomial.map (algebraMap A F))
        (Ideal.span (Set.range g)) = C.toIdeal
    rw [Ideal.map_span, ← Set.range_comp']
    change Ideal.span
      (Set.range (fun i => MvPolynomial.map (algebraMap A F) (g i))) = C.toIdeal
    rw [ideal_span_cleared_generators_eq f g d hd hg]
    change Ideal.span (Set.range ((↑) : ι → MvPolynomial (Fin 4) F)) = C.toIdeal
    rw [Subtype.range_coe]
    exact hCT.symm

/-- If the generic curve lies on a cubic defined over the base domain,
its homogeneous model can be chosen to lie on that cubic over the base. -/
theorem exists_homogeneousIdeal_spread_containing_cubic
    {A F : Type u}
    [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F]
    (p : MvPolynomial (Fin 4) A) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hpC : MvPolynomial.map (algebraMap A F) p ∈ C.toIdeal) :
    ∃ J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A),
      J.toIdeal.FG ∧ p ∈ J.toIdeal ∧
        Ideal.map (MvPolynomial.map (algebraMap A F)) J.toIdeal = C.toIdeal := by
  classical
  obtain ⟨J₀, hfg, hmap⟩ :=
    exists_homogeneousIdeal_spread_of_fractionField (A := A) (F := F) C
  let H : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A) :=
    ⟨Ideal.span ({p} : Set (MvPolynomial (Fin 4) A)),
      Ideal.homogeneous_span _ _ (by
        intro x hx
        simp only [Set.mem_singleton_iff] at hx
        subst x
        exact SetLike.isHomogeneousElem_coe ⟨p, hp⟩)⟩
  refine ⟨J₀ ⊔ H, ?_, ?_, ?_⟩
  · rw [HomogeneousIdeal.toIdeal_sup]
    obtain ⟨S, hS⟩ := hfg
    refine ⟨insert p S, ?_⟩
    change Ideal.span (↑(insert p S) : Set (MvPolynomial (Fin 4) A)) =
      J₀.toIdeal ⊔ H.toIdeal
    rw [Finset.coe_insert, Ideal.span_insert, hS]
    change Ideal.span ({p} : Set (MvPolynomial (Fin 4) A)) ⊔ J₀.toIdeal =
      J₀.toIdeal ⊔ Ideal.span ({p} : Set (MvPolynomial (Fin 4) A))
    exact sup_comm (Ideal.span ({p} : Set (MvPolynomial (Fin 4) A))) J₀.toIdeal
  · exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton p))
  · rw [HomogeneousIdeal.toIdeal_sup, Ideal.map_sup, hmap]
    have hH : Ideal.map (MvPolynomial.map (algebraMap A F)) H.toIdeal ≤
        C.toIdeal := by
      change Ideal.map (MvPolynomial.map (algebraMap A F))
        (Ideal.span ({p} : Set (MvPolynomial (Fin 4) A))) ≤ C.toIdeal
      rw [Ideal.map_span, Set.image_singleton]
      exact (Ideal.span_singleton_le_iff_mem C.toIdeal).mpr hpC
    exact sup_eq_left.mpr hH

/-- The projective model of an ideal containing the cubic equation is a
closed subscheme of the cubic family over the coefficient ring. -/
noncomputable def homogeneousModelToCubic
    {A : Type u} [CommRing A]
    (p : MvPolynomial (Fin 4) A) (hp : p.IsHomogeneous 3)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A))
    (hpJ : p ∈ J.toIdeal) :
    AllCharacteristics.HomogeneousProjective.scheme J ⟶
      AllCharacteristics.HomogeneousProjective.hypersurface p hp :=
  schemeQuotientMap
    (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) J
    (by
      apply Ideal.span_le.mpr
      rintro x rfl
      exact hpJ)

theorem homogeneousModelToCubic_closedImmersion
    {A : Type u} [CommRing A]
    (p : MvPolynomial (Fin 4) A) (hp : p.IsHomogeneous 3)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A))
    (hpJ : p ∈ J.toIdeal) :
    AlgebraicGeometry.IsClosedImmersion (homogeneousModelToCubic p hp J hpJ) := by
  unfold homogeneousModelToCubic
  exact schemeQuotientMap_closedImmersion _ _ _

theorem homogeneousModelToCubic_toBase
    {A : Type u} [CommRing A]
    (p : MvPolynomial (Fin 4) A) (hp : p.IsHomogeneous 3)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A))
    (hpJ : p ∈ J.toIdeal) :
    homogeneousModelToCubic p hp J hpJ ≫
      AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp =
        AllCharacteristics.HomogeneousProjective.toBase J := by
  exact schemeQuotientMap_toBase
    (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) J _

theorem homogeneousModelToCubic_comp_ambient
    {A : Type u} [CommRing A]
    (p : MvPolynomial (Fin 4) A) (hp : p.IsHomogeneous 3)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A))
    (hpJ : p ∈ J.toIdeal) :
    homogeneousModelToCubic p hp J hpJ ≫
      AllCharacteristics.HomogeneousProjective.hypersurfaceToAmbient p hp =
        AllCharacteristics.HomogeneousProjective.quotientProjMap J := by
  exact schemeQuotientMap_comp_quotientProjMap
    (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) J _

/-- A homogeneous quotient immersion commutes with coefficient change. -/
theorem schemeQuotientMap_coefficient_naturality
    {A F : Type u} [CommRing A] [CommRing F]
    (f : A →+* F)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A))
    (I' J' : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hIJ : I.toIdeal ≤ J.toIdeal) (hI'J' : I'.toIdeal ≤ J'.toIdeal)
    (hI : Ideal.map (MvPolynomial.map f) I.toIdeal = I'.toIdeal)
    (hJ : Ideal.map (MvPolynomial.map f) J.toIdeal = J'.toIdeal) :
    AllCharacteristics.HomogeneousProjective.projectiveCoefficientMap f J J' hJ ≫
      schemeQuotientMap I J hIJ =
    schemeQuotientMap I' J' hI'J' ≫
      AllCharacteristics.HomogeneousProjective.projectiveCoefficientMap f I I' hI := by
  apply (cancel_mono (AllCharacteristics.HomogeneousProjective.quotientProjMap I)).mp
  rw [Category.assoc, schemeQuotientMap_comp_quotientProjMap,
    AllCharacteristics.HomogeneousProjective.projectiveCoefficientMap_comp_quotientProjMap]
  rw [Category.assoc,
    AllCharacteristics.HomogeneousProjective.projectiveCoefficientMap_comp_quotientProjMap,
    ← Category.assoc, schemeQuotientMap_comp_quotientProjMap]

/-- Coefficient change commutes with the model's closed immersion into the
cubic.  In particular, the generic-fibre embedding is the original embedding
of the function-field curve into the generic cubic. -/
theorem homogeneousModelToCubic_baseChange_naturality
    {A F : Type u} [CommRing A] [CommRing F]
    (f : A →+* F)
    (p : MvPolynomial (Fin 4) A) (hp : p.IsHomogeneous 3)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hpJ : p ∈ J.toIdeal)
    (hpC : MvPolynomial.map f p ∈ C.toIdeal)
    (hJC : Ideal.map (MvPolynomial.map f) J.toIdeal = C.toIdeal) :
    AllCharacteristics.HomogeneousProjective.projectiveCoefficientMap f J C hJC ≫
        homogeneousModelToCubic p hp J hpJ =
      homogeneousModelToCubic (MvPolynomial.map f p) (hp.map f) C hpC ≫
        AllCharacteristics.HomogeneousProjective.projectiveCoefficientMap f
          (AllCharacteristics.HomogeneousProjective.equationIdeal p hp)
          (AllCharacteristics.HomogeneousProjective.equationIdeal
            (MvPolynomial.map f p) (hp.map f))
          (AllCharacteristics.HomogeneousProjective.equationIdeal_map f p hp) := by
  exact schemeQuotientMap_coefficient_naturality f
    (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) J
    (AllCharacteristics.HomogeneousProjective.equationIdeal
      (MvPolynomial.map f p) (hp.map f)) C _ _
    (AllCharacteristics.HomogeneousProjective.equationIdeal_map f p hp) hJC

/-- Over a Noetherian coefficient ring, the proper projective model is
locally of finite presentation over the base. -/
theorem homogeneousModel_locallyOfFinitePresentation
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A)) :
    AlgebraicGeometry.LocallyOfFinitePresentation
      (AllCharacteristics.HomogeneousProjective.toBase J) := by
  rw [AlgebraicGeometry.LocallyOfFinitePresentation.iff_locallyOfFiniteType]
  infer_instance

/-- An irreducible generic curve has a canonical prime homogeneous model:
contract its ideal along the polynomial coefficient map.  Over a Noetherian
base this model is finitely generated, and extending it back to the fraction
field recovers the original ideal exactly. -/
theorem exists_primeHomogeneousIdeal_spread_of_fractionField
    {A F : Type u}
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hprime : C.toIdeal.IsPrime) :
    ∃ J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A),
      J.toIdeal.FG ∧ J.toIdeal.IsPrime ∧
        Ideal.map (MvPolynomial.map (algebraMap A F)) J.toIdeal = C.toIdeal ∧
        (∀ q : MvPolynomial (Fin 4) A,
          q ∈ J.toIdeal ↔ MvPolynomial.map (algebraMap A F) q ∈ C.toIdeal) ∧
        ∀ a : A, MvPolynomial.C a ∈ J.toIdeal → a = 0 := by
  let φ : MvPolynomial (Fin 4) A →+* MvPolynomial (Fin 4) F :=
    MvPolynomial.map (algebraMap A F)
  let G := AllCharacteristics.HomogeneousProjective.ambientCoefficientGradedRingHom
    (σ := Fin 4) (algebraMap A F)
  let J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A) := C.comap G
  have hJ : J.toIdeal = Ideal.comap φ C.toIdeal := rfl
  obtain ⟨J₀, _, hJ₀⟩ :=
    exists_homogeneousIdeal_spread_of_fractionField (A := A) (F := F) C
  have hJ₀le : J₀.toIdeal ≤ J.toIdeal := by
    intro q hq
    rw [hJ]
    change φ q ∈ C.toIdeal
    rw [← hJ₀]
    exact Ideal.mem_map_of_mem φ hq
  refine ⟨J, IsNoetherian.noetherian J.toIdeal, ?_, ?_, ?_, ?_⟩
  · rw [hJ]
    exact Ideal.comap_isPrime φ C.toIdeal
  · apply le_antisymm
    · rw [hJ]
      exact Ideal.map_comap_le
    · rw [← hJ₀]
      exact Ideal.map_mono hJ₀le
  · intro q
    rw [hJ]
    rfl
  · intro a ha
    by_contra hne
    have hneF : algebraMap A F a ≠ 0 := by
      intro heq
      exact hne ((IsFractionRing.injective A F) (by simpa using heq))
    have hunit : IsUnit (MvPolynomial.C (algebraMap A F a) :
        MvPolynomial (Fin 4) F) :=
      (isUnit_iff_ne_zero.mpr hneF).map (MvPolynomial.C : F →+* MvPolynomial (Fin 4) F)
    have hmem : MvPolynomial.C (algebraMap A F a) ∈ C.toIdeal := by
      have h := ha
      rw [hJ] at h
      change MvPolynomial.map (algebraMap A F) (MvPolynomial.C a) ∈ C.toIdeal at h
      simpa only [MvPolynomial.map_C] using h
    exact (Ideal.notMem_of_isUnit C.toIdeal hunit) hmem

/-- If a homogeneous ideal contains no nonzero base constant, the base
coefficient ring embeds in its homogeneous coordinate ring. -/
theorem homogeneousIdeal_coordinateRing_algebraMap_injective
    {A : Type u} [CommRing A]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A))
    (hconstant : ∀ a : A, MvPolynomial.C a ∈ J.toIdeal → a = 0) :
    Function.Injective (algebraMap A
      (AllCharacteristics.HomogeneousProjective.CoordinateRing J)) := by
  apply (injective_iff_map_eq_zero (algebraMap A
    (AllCharacteristics.HomogeneousProjective.CoordinateRing J))).mpr
  intro a ha
  apply hconstant a
  have hzero : Ideal.Quotient.mk J.toIdeal (MvPolynomial.C a) = 0 := by
    exact ha
  exact Ideal.Quotient.eq_zero_iff_mem.mp hzero

/-- A prime homogeneous model whose base constants survive has a
torsion-free homogeneous coordinate ring over the coefficient domain. -/
theorem homogeneousIdeal_coordinateRing_isTorsionFree
    {A : Type u} [CommRing A] [IsDomain A]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A))
    (hprimeJ : J.toIdeal.IsPrime)
    (hconstant : ∀ a : A, MvPolynomial.C a ∈ J.toIdeal → a = 0) :
    Module.IsTorsionFree A
      (AllCharacteristics.HomogeneousProjective.CoordinateRing J) := by
  letI : IsDomain (AllCharacteristics.HomogeneousProjective.CoordinateRing J) :=
    (Ideal.Quotient.isDomain_iff_prime J.toIdeal).mpr hprimeJ
  exact (Module.isTorsionFree_iff_algebraMap_injective).mpr
    (homogeneousIdeal_coordinateRing_algebraMap_injective J hconstant)

/-- If ideal membership is reflected by coefficient change, then the
associated map of homogeneous coordinate rings is injective. -/
theorem coordinateCoefficientMap_injective_of_membership_iff
    {A F : Type u} [CommRing A] [CommRing F]
    (f : A →+* F)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hmap : Ideal.map (MvPolynomial.map f) J.toIdeal = C.toIdeal)
    (hmem : ∀ q : MvPolynomial (Fin 4) A,
      q ∈ J.toIdeal ↔ MvPolynomial.map f q ∈ C.toIdeal) :
    Function.Injective
      (AllCharacteristics.HomogeneousProjective.coordinateCoefficientMap
        f J C hmap) := by
  apply (injective_iff_map_eq_zero
    (AllCharacteristics.HomogeneousProjective.coordinateCoefficientMap
      f J C hmap)).mpr
  intro x hx
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [AllCharacteristics.HomogeneousProjective.coordinateCoefficientMap_mk] at hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    ((hmem q).mpr (Ideal.Quotient.eq_zero_iff_mem.mp hx))

/-- The prime contracted model embeds as a graded coordinate ring in the
generic curve's homogeneous coordinate ring. -/
theorem exists_primeHomogeneousIdeal_spread_with_injective_generic_coordinateMap
    {A F : Type u}
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hprime : C.toIdeal.IsPrime) :
    ∃ J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A),
      J.toIdeal.FG ∧ J.toIdeal.IsPrime ∧
        ∃ hmap : Ideal.map (MvPolynomial.map (algebraMap A F)) J.toIdeal = C.toIdeal,
          Function.Injective
            (AllCharacteristics.HomogeneousProjective.coordinateCoefficientMap
              (algebraMap A F) J C hmap) := by
  obtain ⟨J, hfg, hprimeJ, hmap, hmem, _⟩ :=
    exists_primeHomogeneousIdeal_spread_of_fractionField
      (A := A) (F := F) C hprime
  exact ⟨J, hfg, hprimeJ, hmap,
    coordinateCoefficientMap_injective_of_membership_iff
      (algebraMap A F) J C hmap hmem⟩

/-- The quotient by a homogeneous ideal becomes its coefficient-extended
quotient after inverting all nonzero base coefficients. -/
theorem coordinateRing_canonical_generic_isLocalization
    {A F : Type u} [CommRing A] [IsDomain A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A)) :
    letI : Algebra (MvPolynomial (Fin 4) A ⧸ J.toIdeal)
      (MvPolynomial (Fin 4) F ⧸
        Ideal.map (MvPolynomial.map (algebraMap A F)) J.toIdeal) :=
      (Ideal.quotientMap
        (Ideal.map (MvPolynomial.map (algebraMap A F)) J.toIdeal)
        (MvPolynomial.map (algebraMap A F))
        (Ideal.map_le_iff_le_comap.mp le_rfl)).toAlgebra
    IsLocalization
      (((nonZeroDivisors A).map
        (MvPolynomial.C : A →+* MvPolynomial (Fin 4) A)).map
        (Ideal.Quotient.mk J.toIdeal))
      (MvPolynomial (Fin 4) F ⧸
        Ideal.map (MvPolynomial.map (algebraMap A F)) J.toIdeal) := by
  let M : Submonoid (MvPolynomial (Fin 4) A) :=
    (nonZeroDivisors A).map (MvPolynomial.C : A →+* MvPolynomial (Fin 4) A)
  letI : IsLocalization M (MvPolynomial (Fin 4) F) := by
    dsimp [M]
    infer_instance
  letI : Algebra (MvPolynomial (Fin 4) A ⧸ J.toIdeal)
      (MvPolynomial (Fin 4) F ⧸
        Ideal.map (MvPolynomial.map (algebraMap A F)) J.toIdeal) :=
    (Ideal.quotientMap
      (Ideal.map (MvPolynomial.map (algebraMap A F)) J.toIdeal)
      (MvPolynomial.map (algebraMap A F))
      (Ideal.map_le_iff_le_comap.mp le_rfl)).toAlgebra
  change IsLocalization (M.map (Ideal.Quotient.mk J.toIdeal))
    (MvPolynomial (Fin 4) F ⧸
      Ideal.map (MvPolynomial.map (algebraMap A F)) J.toIdeal)
  exact IsLocalization.of_surjective M (MvPolynomial (Fin 4) F)
    (Ideal.Quotient.mk J.toIdeal) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (Ideal.map (MvPolynomial.map (algebraMap A F)) J.toIdeal))
    Ideal.Quotient.mk_surjective (by
      ext q
      · rfl
      · change Ideal.Quotient.mk
            (Ideal.map (MvPolynomial.map (algebraMap A F)) J.toIdeal)
            (MvPolynomial.map (algebraMap A F) (MvPolynomial.X q)) =
          (Ideal.quotientMap
            (Ideal.map (MvPolynomial.map (algebraMap A F)) J.toIdeal)
            (MvPolynomial.map (algebraMap A F))
            (Ideal.map_le_iff_le_comap.mp le_rfl))
            (Ideal.Quotient.mk J.toIdeal (MvPolynomial.X q))
        rw [Ideal.quotientMap_mk]) (by simp)

/-- The localization identification is unchanged when the generic ideal is
presented by an equal ideal rather than by the canonical extension term. -/
theorem coordinateRing_generic_isLocalization
    {A F : Type u} [CommRing A] [IsDomain A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A))
    (K : Ideal (MvPolynomial (Fin 4) F))
    (hmap : Ideal.map (MvPolynomial.map (algebraMap A F)) J.toIdeal = K) :
    letI : Algebra (AllCharacteristics.HomogeneousProjective.CoordinateRing J)
      (MvPolynomial (Fin 4) F ⧸ K) :=
      (Ideal.quotientMap K (MvPolynomial.map (algebraMap A F))
        (Ideal.map_le_iff_le_comap.mp hmap.le)).toAlgebra
    IsLocalization
      (((nonZeroDivisors A).map
        (MvPolynomial.C : A →+* MvPolynomial (Fin 4) A)).map
        (Ideal.Quotient.mk J.toIdeal))
      (MvPolynomial (Fin 4) F ⧸ K) := by
  subst K
  exact coordinateRing_canonical_generic_isLocalization (A := A) (F := F) J

/-- The actual homogeneous coordinate ring of the generic curve is the
localization of the spread-out model at nonzero base coefficients. -/
theorem projectiveCurve_coordinateRing_generic_isLocalization
    {A F : Type u} [CommRing A] [IsDomain A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hmap : Ideal.map (MvPolynomial.map (algebraMap A F)) J.toIdeal = C.toIdeal) :
    letI : Algebra (AllCharacteristics.HomogeneousProjective.CoordinateRing J)
      (AllCharacteristics.HomogeneousProjective.CoordinateRing C) :=
      (AllCharacteristics.HomogeneousProjective.coordinateCoefficientMap
        (algebraMap A F) J C hmap).toAlgebra
    IsLocalization
      (((nonZeroDivisors A).map
        (MvPolynomial.C : A →+* MvPolynomial (Fin 4) A)).map
        (Ideal.Quotient.mk J.toIdeal))
      (AllCharacteristics.HomogeneousProjective.CoordinateRing C) := by
  exact coordinateRing_generic_isLocalization (A := A) (F := F) J C.toIdeal hmap

/-- A prime generic curve on a cubic spreads to a prime homogeneous
closed subscheme of the whole cubic family, with no extra vertical
components in its defining ideal. -/
theorem exists_primeHomogeneousIdeal_spread_containing_cubic
    {A F : Type u}
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (p : MvPolynomial (Fin 4) A) (_hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hprime : C.toIdeal.IsPrime)
    (hpC : MvPolynomial.map (algebraMap A F) p ∈ C.toIdeal) :
    ∃ J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A),
      J.toIdeal.FG ∧ J.toIdeal.IsPrime ∧ p ∈ J.toIdeal ∧
        Ideal.map (MvPolynomial.map (algebraMap A F)) J.toIdeal = C.toIdeal ∧
        ∀ a : A, MvPolynomial.C a ∈ J.toIdeal → a = 0 := by
  obtain ⟨J, hfg, hprimeJ, hmap, hmem, hconstant⟩ :=
    exists_primeHomogeneousIdeal_spread_of_fractionField
      (A := A) (F := F) C hprime
  exact ⟨J, hfg, hprimeJ, (hmem p).mpr hpC, hmap, hconstant⟩

/-- The function-field projective curve is the actual categorical generic
fibre of a homogeneous projective model over the coefficient domain. -/
theorem exists_projectiveCurve_genericFiber_model
    {A F : Type u}
    [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) :
    ∃ J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A),
      J.toIdeal.FG ∧
        AlgebraicGeometry.IsProper
          (AllCharacteristics.HomogeneousProjective.toBase J) ∧
        Nonempty (AllCharacteristics.HomogeneousProjective.scheme C ≅
          CategoryTheory.Limits.pullback
            (AllCharacteristics.HomogeneousProjective.toBase J)
            (AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom (algebraMap A F)))) := by
  obtain ⟨J, hfg, hmap⟩ :=
    exists_homogeneousIdeal_spread_of_fractionField (A := A) (F := F) C
  refine ⟨J, hfg, inferInstance, ?_⟩
  exact ⟨AllCharacteristics.HomogeneousProjective.projectiveBaseChangeIso
    (algebraMap A F) J C hmap⟩

/-- A generic projective curve lying on a cubic over the base has a proper
projective model cut out by a finite homogeneous ideal containing that cubic.
Its generic fibre is the prescribed curve. -/
theorem exists_projectiveCurve_genericFiber_model_containing_cubic
    {A F : Type u}
    [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F]
    (p : MvPolynomial (Fin 4) A) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hpC : MvPolynomial.map (algebraMap A F) p ∈ C.toIdeal) :
    ∃ J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A),
      J.toIdeal.FG ∧ p ∈ J.toIdeal ∧
        AlgebraicGeometry.IsProper
          (AllCharacteristics.HomogeneousProjective.toBase J) ∧
        Nonempty (AllCharacteristics.HomogeneousProjective.scheme C ≅
          CategoryTheory.Limits.pullback
            (AllCharacteristics.HomogeneousProjective.toBase J)
            (AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom (algebraMap A F)))) := by
  obtain ⟨J, hfg, hpJ, hmap⟩ :=
    exists_homogeneousIdeal_spread_containing_cubic
      (A := A) (F := F) p hp C hpC
  refine ⟨J, hfg, hpJ, inferInstance, ?_⟩
  exact ⟨AllCharacteristics.HomogeneousProjective.projectiveBaseChangeIso
    (algebraMap A F) J C hmap⟩

/-- The generic curve spreads as a projective closed subscheme of the cubic
family itself, and the closed subscheme has the prescribed generic fibre. -/
theorem exists_projectiveCurve_genericFiber_closedModel_in_cubic
    {A F : Type u}
    [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F]
    (p : MvPolynomial (Fin 4) A) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hpC : MvPolynomial.map (algebraMap A F) p ∈ C.toIdeal) :
    ∃ J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A),
      J.toIdeal.FG ∧
        ∃ i : AllCharacteristics.HomogeneousProjective.scheme J ⟶
            AllCharacteristics.HomogeneousProjective.hypersurface p hp,
          AlgebraicGeometry.IsClosedImmersion i ∧
          i ≫ AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp =
            AllCharacteristics.HomogeneousProjective.toBase J ∧
          Nonempty (AllCharacteristics.HomogeneousProjective.scheme C ≅
            CategoryTheory.Limits.pullback
              (AllCharacteristics.HomogeneousProjective.toBase J)
              (AlgebraicGeometry.Spec.map
                (CommRingCat.ofHom (algebraMap A F)))) := by
  obtain ⟨J, hfg, hpJ, _, hgeneric⟩ :=
    exists_projectiveCurve_genericFiber_model_containing_cubic
      (A := A) (F := F) p hp C hpC
  exact ⟨J, hfg, homogeneousModelToCubic p hp J hpJ,
    homogeneousModelToCubic_closedImmersion p hp J hpJ,
    homogeneousModelToCubic_toBase p hp J hpJ, hgeneric⟩

/-- On a Noetherian affine base, the spread-out cubic curve is proper and
locally of finite presentation, the finiteness hypotheses needed before
constructing a dense flat locus. -/
theorem exists_projectiveCurve_genericFiber_finitelyPresentedModel_in_cubic
    {A F : Type u}
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (p : MvPolynomial (Fin 4) A) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hpC : MvPolynomial.map (algebraMap A F) p ∈ C.toIdeal) :
    ∃ J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A),
      J.toIdeal.FG ∧
        AlgebraicGeometry.IsProper
          (AllCharacteristics.HomogeneousProjective.toBase J) ∧
        AlgebraicGeometry.LocallyOfFinitePresentation
          (AllCharacteristics.HomogeneousProjective.toBase J) ∧
        ∃ i : AllCharacteristics.HomogeneousProjective.scheme J ⟶
            AllCharacteristics.HomogeneousProjective.hypersurface p hp,
          AlgebraicGeometry.IsClosedImmersion i ∧
          i ≫ AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp =
            AllCharacteristics.HomogeneousProjective.toBase J ∧
          Nonempty (AllCharacteristics.HomogeneousProjective.scheme C ≅
            CategoryTheory.Limits.pullback
              (AllCharacteristics.HomogeneousProjective.toBase J)
              (AlgebraicGeometry.Spec.map
                (CommRingCat.ofHom (algebraMap A F)))) := by
  obtain ⟨J, hfg, i, hi, hib, hgeneric⟩ :=
    exists_projectiveCurve_genericFiber_closedModel_in_cubic
      (A := A) (F := F) p hp C hpC
  exact ⟨J, hfg, inferInstance,
    homogeneousModel_locallyOfFinitePresentation J,
    i, hi, hib, hgeneric⟩

/-- An irreducible generic curve has a prime, finitely presented projective
model inside the cubic family.  The prime contraction avoids adding vertical
components to the total-space defining ideal. -/
theorem exists_primeProjectiveCurve_genericFiber_finitelyPresentedModel_in_cubic
    {A F : Type u}
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (p : MvPolynomial (Fin 4) A) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hprime : C.toIdeal.IsPrime)
    (hpC : MvPolynomial.map (algebraMap A F) p ∈ C.toIdeal) :
    ∃ J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) A),
      J.toIdeal.FG ∧ J.toIdeal.IsPrime ∧
        (∀ a : A, MvPolynomial.C a ∈ J.toIdeal → a = 0) ∧
        IsDomain (AllCharacteristics.HomogeneousProjective.CoordinateRing J) ∧
        Function.Injective (algebraMap A
          (AllCharacteristics.HomogeneousProjective.CoordinateRing J)) ∧
        Module.IsTorsionFree A
          (AllCharacteristics.HomogeneousProjective.CoordinateRing J) ∧
        AlgebraicGeometry.IsProper
          (AllCharacteristics.HomogeneousProjective.toBase J) ∧
        AlgebraicGeometry.LocallyOfFinitePresentation
          (AllCharacteristics.HomogeneousProjective.toBase J) ∧
        ∃ i : AllCharacteristics.HomogeneousProjective.scheme J ⟶
            AllCharacteristics.HomogeneousProjective.hypersurface p hp,
          AlgebraicGeometry.IsClosedImmersion i ∧
          i ≫ AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp =
            AllCharacteristics.HomogeneousProjective.toBase J ∧
          Nonempty (AllCharacteristics.HomogeneousProjective.scheme C ≅
            CategoryTheory.Limits.pullback
              (AllCharacteristics.HomogeneousProjective.toBase J)
              (AlgebraicGeometry.Spec.map
                (CommRingCat.ofHom (algebraMap A F)))) := by
  obtain ⟨J, hfg, hprimeJ, hpJ, hmap, hconstant⟩ :=
    exists_primeHomogeneousIdeal_spread_containing_cubic
      (A := A) (F := F) p hp C hprime hpC
  refine ⟨J, hfg, hprimeJ, hconstant,
    (Ideal.Quotient.isDomain_iff_prime J.toIdeal).mpr hprimeJ,
    homogeneousIdeal_coordinateRing_algebraMap_injective J hconstant,
    homogeneousIdeal_coordinateRing_isTorsionFree J hprimeJ hconstant,
    inferInstance,
    homogeneousModel_locallyOfFinitePresentation J,
    homogeneousModelToCubic p hp J hpJ,
    homogeneousModelToCubic_closedImmersion p hp J hpJ,
    homogeneousModelToCubic_toBase p hp J hpJ, ?_⟩
  exact ⟨AllCharacteristics.HomogeneousProjective.projectiveBaseChangeIso
    (algebraMap A F) J C hmap⟩

end PfaffianDescent
