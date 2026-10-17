import PfaffianDescent.VoisinQuadraticRestrictionKernelUniversalFamily
import PfaffianDescent.VoisinQuadraticUniversalIntersectionFamily
import PfaffianDescent.VoisinDegreeTenResidualEnd

/-!
# Generic finiteness in the quadratic kernel through a finite datum

A regular member of the full quadratic vanishing kernel is represented by
coordinates in its chosen basis. It supplies a finite witness fibre for the
actual universal projective intersection restricted to that kernel.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
  [FiniteDimensional K A]

private theorem quadraticRestrictionKernelFrame_specializes_to
    (x : Fin 4 → A)
    (r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 2)
    (hrvan : r.eval₂ (algebraMap K A) x = 0) :
    let b := quadraticRestrictionKernelBasis (K := K) x
    let rW : LinearMap.ker (homogeneousSectionRestriction (K := K) x 2) :=
      ⟨⟨r, hr⟩, by
        apply LinearMap.mem_ker.mpr
        simpa only [homogeneousSectionRestriction_apply] using hrvan⟩
    let t := b.repr rW
    (cubicTwoQuadricUniversalQuadric
      (quadraticRestrictionKernelFrame (K := K) x)).map
        (MvPolynomial.eval₂Hom (RingHom.id K) t) = r := by
  dsimp only
  rw [cubicTwoQuadricUniversalQuadric_map]
  simp only [MvPolynomial.map_id]
  let rW : LinearMap.ker (homogeneousSectionRestriction (K := K) x 2) :=
    ⟨⟨r, hr⟩, by
      apply LinearMap.mem_ker.mpr
      simpa only [homogeneousSectionRestriction_apply] using hrvan⟩
  have hrepr := (quadraticRestrictionKernelBasis (K := K) x).sum_repr rW
  have hval := congrArg
    (fun z : LinearMap.ker (homogeneousSectionRestriction (K := K) x 2) => z.1.1)
    hrepr
  simp only [Submodule.coe_sum, Submodule.coe_smul,
    MvPolynomial.smul_eq_C_mul] at hval
  exact hval

/-- One regular quadric through the datum makes the full restriction-kernel
intersection family finite near its generic parameter. -/
theorem cubicTwoQuadricRestrictionKernel_exists_genericFiniteNeighborhood_of_regularMember
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (x : Fin 4 → A)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hrvan : r.eval₂ (algebraMap K A) x = 0)
    (hregular : ∀ F : MvPolynomial (Fin 4) K,
      r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) :
    ∃ V : (Spec (.of (MvPolynomial
        (Fin (finrank K (LinearMap.ker
          (homogeneousSectionRestriction (K := K) x 2)))) K))).Opens,
      genericPoint (Spec (.of (MvPolynomial
        (Fin (finrank K (LinearMap.ker
          (homogeneousSectionRestriction (K := K) x 2)))) K))) ∈ V ∧
      IsFinite ((cubicTwoQuadricUniversalIntersectionToCone p q hp hq
        (quadraticRestrictionKernelFrame (K := K) x)) ∣_ V) := by
  let rW : LinearMap.ker (homogeneousSectionRestriction (K := K) x 2) :=
    ⟨⟨r, hr⟩, by
      apply LinearMap.mem_ker.mpr
      simpa only [homogeneousSectionRestriction_apply] using hrvan⟩
  let t := (quadraticRestrictionKernelBasis (K := K) x).repr rW
  have hspec :
      (cubicTwoQuadricUniversalQuadric
        (quadraticRestrictionKernelFrame (K := K) x)).map
        (MvPolynomial.eval₂Hom (RingHom.id K) t) = r :=
    quadraticRestrictionKernelFrame_specializes_to x r hr hrvan
  apply cubicTwoQuadricUniversalIntersection_exists_genericFiniteNeighborhood_of_regularSpecialization
    (RingHom.id K) p q hp hq
    (quadraticRestrictionKernelFrame (K := K) x) t
  · simpa only [MvPolynomial.map_id] using hp0
  · simpa only [MvPolynomial.map_id] using hq0
  · simpa only [MvPolynomial.map_id] using hrel
  · intro F hF
    rw [hspec] at hF
    simpa only [MvPolynomial.map_id] using
      (hregular F (by simpa only [MvPolynomial.map_id] using hF))

/-- The generic finite-open property of the complete quadratic restriction
kernel, with the first quadric fixed. -/
def QuadraticRestrictionKernelGenericallyFinite
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (x : Fin 4 → A) : Prop :=
  ∃ V : (Spec (.of (MvPolynomial
      (Fin (finrank K (LinearMap.ker
        (homogeneousSectionRestriction (K := K) x 2)))) K))).Opens,
    genericPoint (Spec (.of (MvPolynomial
      (Fin (finrank K (LinearMap.ker
        (homogeneousSectionRestriction (K := K) x 2)))) K))) ∈ V ∧
    IsFinite ((cubicTwoQuadricUniversalIntersectionToCone p q hp hq
      (quadraticRestrictionKernelFrame (K := K) x)) ∣_ V)

/-- A regular member of the complete quadratic kernel gives its generic
finite-open property. -/
theorem QuadraticRestrictionKernelGenericallyFinite.of_regularMember
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) (x : Fin 4 → A)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hrvan : r.eval₂ (algebraMap K A) x = 0)
    (hregular : ∀ F : MvPolynomial (Fin 4) K,
      r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) :
    QuadraticRestrictionKernelGenericallyFinite p q hp hq x :=
  cubicTwoQuadricRestrictionKernel_exists_genericFiniteNeighborhood_of_regularMember
    p q r hp hq hr x hp0 hq0 hrel hrvan hregular

/-- The degree-eight regular-pair condition gives generic finiteness for the
actual quadratic system through the datum in each normalized presentation. -/
theorem DegreeEightRegularQuadricPairExists.genericFiniteQuadraticKernel
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hpair : DegreeEightRegularQuadricPairExists p hp D₈) :
    letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
    letI := finiteSchemeCoefficientAlgebra
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∀ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤)),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) →
      ∃ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous 2),
        q ≠ 0 ∧ IsRelPrime p q ∧
        QuadraticRestrictionKernelGenericallyFinite p q hp hq x := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI : Module.Finite K Γ(D₈.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  intro x hx
  obtain ⟨q, hq, _hqvan, hq0, hrel, r, hr, hrvan, hregular⟩ := hpair x hx
  exact ⟨q, hq, hq0, hrel,
    QuadraticRestrictionKernelGenericallyFinite.of_regularMember
      p q r hp hq hr x hp0 hq0 hrel hrvan hregular⟩

end PfaffianDescent
