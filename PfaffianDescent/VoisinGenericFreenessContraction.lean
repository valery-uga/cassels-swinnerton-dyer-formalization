import PfaffianDescent.VoisinGenericFreenessLeadingMonomials
import PfaffianDescent.VoisinGenericFreenessCoefficientMap
import PfaffianDescent.VoisinGenericFreenessDenominatorSpreading
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import AllCharacteristics.HomogeneousProjective
import AllCharacteristics.ProjectiveBaseChange
import AllCharacteristics.HomogeneousProjectiveAmbient
import AllCharacteristics.ProjectiveUnitCoefficientFlatness

/-!
# Leading covers for contracted generic ideals

Contracting the generic ideal along an injective coefficient map preserves
the generic leading-exponent cover whenever the selected generators have
degree-preserving lifts. This avoids a Buchberger step for the contracted
model used in the Voisin spreading argument.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u v

/-- The ideal quotient and the quotient by the same ideal viewed as a
submodule have the same underlying polynomial classes and scalar action. -/
def idealQuotientLinearEquivSubmoduleQuotient
    {R : Type u} [CommRing R]
    (J : Ideal (MvPolynomial (Fin 4) R)) :
    (MvPolynomial (Fin 4) R ⧸ J) ≃ₗ[R]
      (MvPolynomial (Fin 4) R ⧸ Submodule.restrictScalars R J) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/-- A principal localization of a domain at a nonzero element embeds in its
fraction field, compatibly with the original coefficient map. -/
theorem exists_injective_away_to_fractionField
    {A : Type u} {F : Type v}
    [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F]
    (e : A) (he : e ≠ 0) :
    ∃ φ : Localization.Away e →+* F,
      Function.Injective φ ∧
        ∀ a : A, φ (algebraMap A (Localization.Away e) a) = algebraMap A F a := by
  have heF : algebraMap A F e ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective A F).ne he
  let φ : Localization.Away e →+* F :=
    Localization.awayLift (algebraMap A F) e (isUnit_iff_ne_zero.mpr heF)
  have hAinj : Function.Injective (algebraMap A (Localization.Away e)) :=
    IsLocalization.injective (Localization.Away e)
      (powers_le_nonZeroDivisors_of_noZeroDivisors he)
  refine ⟨φ, ?_, ?_⟩
  · apply (IsLocalization.injective_iff_map_algebraMap_eq
      (Submonoid.powers e) φ).mpr
    intro a b
    simp only [φ, Localization.awayLift, IsLocalization.Away.lift_eq]
    constructor
    · intro hab
      exact congrArg (algebraMap A F) (hAinj hab)
    · intro hab
      exact congrArg (algebraMap A (Localization.Away e))
        ((IsFractionRing.injective A F) hab)
  · intro a
    exact IsLocalization.Away.lift_eq e (isUnit_iff_ne_zero.mpr heF) a

/-- The lifted generic leading set covers every nonzero element of the
contracted ideal. Membership and leading exponents both reflect along the
injective coefficient map. -/
theorem leading_cover_of_ideal_comap
    {R : Type u} {F : Type v} [CommRing R] [Field F]
    (φ : R →+* F) (hφ : Function.Injective φ)
    (m : MonomialOrder (Fin 4))
    (I : Ideal (MvPolynomial (Fin 4) F))
    (G : Set (MvPolynomial (Fin 4) F))
    (hcover : ∀ f ∈ I, f ≠ 0 → ∃ x ∈ G, m.degree x ≤ m.degree f)
    (g : G → MvPolynomial (Fin 4) R)
    (hmap : ∀ x : G, MvPolynomial.map φ (g x) ∈ I)
    (hdeg : ∀ x : G, m.degree (g x) = m.degree (x : MvPolynomial (Fin 4) F)) :
    Set.range g ⊆ Ideal.comap (MvPolynomial.map φ) I ∧
      ∀ p ∈ Ideal.comap (MvPolynomial.map φ) I, p ≠ 0 →
        ∃ y ∈ Set.range g, m.degree y ≤ m.degree p := by
  constructor
  · rintro y ⟨x, rfl⟩
    exact hmap x
  · intro p hp hpne
    have hpf : MvPolynomial.map φ p ∈ I := hp
    have hpfne : MvPolynomial.map φ p ≠ 0 := by
      simpa only [map_zero] using (MvPolynomial.map_injective φ hφ).ne hpne
    obtain ⟨x, hx, hle⟩ := hcover (MvPolynomial.map φ p) hpf hpfne
    refine ⟨g ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    rw [hdeg ⟨x, hx⟩, ← monomialOrder_degree_map_of_injective φ hφ m p]
    exact hle

/-- Once the lifted leading coefficients are units, the contracted generic
ideal has a flat quotient over the coefficient ring. No critical-pair
argument is needed for this contracted ideal. -/
theorem ideal_comap_quotient_flat_of_unit_leading_lifts
    {R : Type u} {F : Type v} [CommRing R] [Field F]
    (φ : R →+* F) (hφ : Function.Injective φ)
    (m : MonomialOrder (Fin 4))
    (I : Ideal (MvPolynomial (Fin 4) F))
    (G : Set (MvPolynomial (Fin 4) F))
    (hcover : ∀ f ∈ I, f ≠ 0 → ∃ x ∈ G, m.degree x ≤ m.degree f)
    (g : G → MvPolynomial (Fin 4) R)
    (hmap : ∀ x : G, MvPolynomial.map φ (g x) ∈ I)
    (hdeg : ∀ x : G, m.degree (g x) = m.degree (x : MvPolynomial (Fin 4) F))
    (hunit : ∀ x : G, IsUnit (m.leadingCoeff (g x))) :
    Module.Flat R
      (MvPolynomial (Fin 4) R ⧸
        Submodule.restrictScalars R (Ideal.comap (MvPolynomial.map φ) I)) := by
  obtain ⟨hsub, hcoverR⟩ :=
    leading_cover_of_ideal_comap φ hφ m I G hcover g hmap hdeg
  apply polynomialQuotient_flat_of_unit_leading_cover m
    (Ideal.comap (MvPolynomial.map φ) I) (Set.range g) hsub
  · rintro y ⟨x, rfl⟩
    exact hunit x
  · exact hcoverR

/-- After inverting a nonzero common multiple of the lifted leading
coefficients, the quotient by the contracted generic ideal is flat on that
principal open. -/
theorem exists_flat_away_contracted_ideal
    {A : Type u} {F : Type v}
    [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F]
    (m : MonomialOrder (Fin 4))
    (I : Ideal (MvPolynomial (Fin 4) F))
    (G : Set (MvPolynomial (Fin 4) F))
    (hcover : ∀ f ∈ I, f ≠ 0 → ∃ x ∈ G, m.degree x ≤ m.degree f)
    (g : G → MvPolynomial (Fin 4) A)
    (hmap : ∀ x : G, MvPolynomial.map (algebraMap A F) (g x) ∈ I)
    (hdeg : ∀ x : G, m.degree (g x) = m.degree (x : MvPolynomial (Fin 4) F))
    (e : A) (he : e ≠ 0)
    (hdiv : ∀ x : G, m.leadingCoeff (g x) ∣ e) :
    ∃ φ : Localization.Away e →+* F,
      Function.Injective φ ∧
        (∀ a : A, φ (algebraMap A (Localization.Away e) a) =
          algebraMap A F a) ∧
        Module.Flat (Localization.Away e)
          (MvPolynomial (Fin 4) (Localization.Away e) ⧸
            Submodule.restrictScalars (Localization.Away e)
              (Ideal.comap (MvPolynomial.map φ) I)) := by
  obtain ⟨φ, hφ, hcomp⟩ :=
    exists_injective_away_to_fractionField (F := F) e he
  let ψ : A →+* Localization.Away e := algebraMap A (Localization.Away e)
  have hψ : Function.Injective ψ :=
    IsLocalization.injective (Localization.Away e)
      (powers_le_nonZeroDivisors_of_noZeroDivisors he)
  let g' : G → MvPolynomial (Fin 4) (Localization.Away e) :=
    fun x => MvPolynomial.map ψ (g x)
  have hcomp' : φ.comp ψ = algebraMap A F := by
    ext a
    exact hcomp a
  have hmap' : ∀ x : G, MvPolynomial.map φ (g' x) ∈ I := by
    intro x
    change MvPolynomial.map φ (MvPolynomial.map ψ (g x)) ∈ I
    rw [MvPolynomial.map_map, hcomp']
    exact hmap x
  have hdeg' : ∀ x : G, m.degree (g' x) =
      m.degree (x : MvPolynomial (Fin 4) F) := by
    intro x
    change m.degree (MvPolynomial.map ψ (g x)) = _
    rw [monomialOrder_degree_map_of_injective ψ hψ m (g x), hdeg x]
  have hunit' : ∀ x : G, IsUnit (m.leadingCoeff (g' x)) := by
    intro x
    exact monomialOrder_isUnit_leadingCoeff_map_of_dvd_unit
      ψ hψ m (g x) e (hdiv x)
      (IsLocalization.Away.algebraMap_isUnit e)
  refine ⟨φ, hφ, hcomp, ?_⟩
  exact ideal_comap_quotient_flat_of_unit_leading_lifts
    φ hφ m I G hcover g' hmap' hdeg' hunit'

/-- The contraction of any four-variable ideal from the fraction field has
a flat polynomial quotient on some nonempty principal open of the base
domain. The ideal on the open is the actual contraction of the generic ideal. -/
theorem exists_flat_principal_open_for_contracted_generic_ideal
    {A : Type u} {F : Type v}
    [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F]
    (m : MonomialOrder (Fin 4))
    (I : Ideal (MvPolynomial (Fin 4) F)) :
    ∃ e : A, e ≠ 0 ∧
      ∃ φ : Localization.Away e →+* F,
        Function.Injective φ ∧
          (∀ a : A, φ (algebraMap A (Localization.Away e) a) =
            algebraMap A F a) ∧
          Ideal.map (MvPolynomial.map φ)
            (Ideal.comap (MvPolynomial.map φ) I) = I ∧
          Module.Flat (Localization.Away e)
            (MvPolynomial (Fin 4) (Localization.Away e) ⧸
              Submodule.restrictScalars (Localization.Away e)
                (Ideal.comap (MvPolynomial.map φ) I)) := by
  obtain ⟨G, _, hsub, hspan, _, hcover, _, _, d, hd, g, _, hg, _, hdeg,
    _, _, e, he, hdiv, _, _, _⟩ :=
    exists_cleared_critical_pair_certificates (A := A) m I
  have hmap : ∀ x : G, MvPolynomial.map (algebraMap A F) (g x) ∈ I := by
    intro x
    rw [hg x]
    exact I.mul_mem_left _ (hsub x.property)
  obtain ⟨φ, hφ, hcomp, hflat⟩ :=
    exists_flat_away_contracted_ideal m I G hcover g hmap hdeg e he hdiv
  refine ⟨e, he, φ, hφ, hcomp, ?_, hflat⟩
  let ψ : A →+* Localization.Away e := algebraMap A (Localization.Away e)
  have hcompRing : φ.comp ψ = algebraMap A F := by
    ext a
    exact hcomp a
  have hgen (x : G) :
      MvPolynomial.map φ (MvPolynomial.map ψ (g x)) =
        MvPolynomial.C (algebraMap A F d) * (x : MvPolynomial (Fin 4) F) := by
    rw [MvPolynomial.map_map, hcompRing, hg x]
  have hdF : algebraMap A F d ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective A F).ne hd
  apply le_antisymm
  · exact Ideal.map_comap_le
  · calc
      I = Ideal.span G := hspan.symm
      _ ≤ Ideal.map (MvPolynomial.map φ)
          (Ideal.comap (MvPolynomial.map φ) I) := by
        apply Ideal.span_le.mpr
        intro x hx
        let y : G := ⟨x, hx⟩
        have hy : MvPolynomial.map ψ (g y) ∈
        Ideal.comap (MvPolynomial.map φ) I := by
          change MvPolynomial.map φ (MvPolynomial.map ψ (g y)) ∈ I
          rw [hgen y]
          exact I.mul_mem_left _ (hsub y.property)
        have hscaled : MvPolynomial.C (algebraMap A F d) * x ∈
        Ideal.map (MvPolynomial.map φ)
          (Ideal.comap (MvPolynomial.map φ) I) := by
          rw [← hgen y]
          exact Ideal.mem_map_of_mem _ hy
        have hback := (Ideal.map (MvPolynomial.map φ)
          (Ideal.comap (MvPolynomial.map φ) I)).mul_mem_left
            (MvPolynomial.C ((algebraMap A F d)⁻¹)) hscaled
        have hcancel : MvPolynomial.C ((algebraMap A F d)⁻¹) *
        (MvPolynomial.C (algebraMap A F d) * x) = x := by
          rw [← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hdF,
            map_one, one_mul]
        exact hcancel ▸ hback

/-- A homogeneous generic ideal has a homogeneous contracted model whose
coordinate algebra is flat after restricting to a nonempty principal open. -/
theorem exists_flat_homogeneous_contracted_model_after_away
    {A F : Type u}
    [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F]
    (m : MonomialOrder (Fin 4))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) :
    ∃ e : A, e ≠ 0 ∧
      ∃ φ : Localization.Away e →+* F,
        Function.Injective φ ∧
          (∀ a : A, φ (algebraMap A (Localization.Away e) a) =
            algebraMap A F a) ∧
          ∃ J : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) (Localization.Away e)),
            J.toIdeal = Ideal.comap (MvPolynomial.map φ) C.toIdeal ∧
              Ideal.map (MvPolynomial.map φ) J.toIdeal = C.toIdeal ∧
              Module.Flat (Localization.Away e) (CoordinateRing J) ∧
              AlgebraicGeometry.Flat (toBase J) ∧
              Nonempty (scheme C ≅
                CategoryTheory.Limits.pullback (toBase J)
                  (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ))) := by
  obtain ⟨e, he, φ, hφ, hcomp, hmap, hflat⟩ :=
    exists_flat_principal_open_for_contracted_generic_ideal (A := A) m C.toIdeal
  let G := ambientCoefficientGradedRingHom (σ := Fin 4) φ
  let J : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (Localization.Away e)) := C.comap G
  have hJ : J.toIdeal = Ideal.comap (MvPolynomial.map φ) C.toIdeal := rfl
  have hflatJ : Module.Flat (Localization.Away e) (CoordinateRing J) := by
    letI : Module.Flat (Localization.Away e)
        (MvPolynomial (Fin 4) (Localization.Away e) ⧸
          Submodule.restrictScalars (Localization.Away e) J.toIdeal) := by
      rw [hJ]
      exact hflat
    exact Module.Flat.of_linearEquiv
      (idealQuotientLinearEquivSubmoduleQuotient J.toIdeal)
  refine ⟨e, he, φ, hφ, hcomp, J, hJ, ?_, hflatJ, ?_, ?_⟩
  · rw [hJ]
    exact hmap
  · letI : Module.Flat (Localization.Away e) (CoordinateRing J) := hflatJ
    exact flat_toBase_of_flat_homogeneous_quotient J
  · exact ⟨projectiveBaseChangeIso φ J C (by simpa only [hJ] using hmap)⟩

end PfaffianDescent
