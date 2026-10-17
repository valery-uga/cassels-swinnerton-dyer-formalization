import PfaffianDescent.QuadraticSkewOriginalCubicForwardPrincipalPlane
import PfaffianDescent.CubicFiniteSubschemeHyperplane
/-! SOURCE ONLY / UNVERIFIED. Actual restriction to the inverse preimage of
the principal plane open, with derived first inverse identity and density
inside the SAME original smooth cubic. No dense-open or birationality premise. -/

noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.ForwardChart004
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective InverseChart
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k]
variable (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
variable (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2)
variable (R : PlaneIndex → MvPolynomial (Fin 4) k) (hR : ∀ i, (R i).IsHomogeneous 2)
variable (N : PlanePolynomial k)

/-- The actual further open on the original cubic chart where the inverse
lands in the actual principal affine-plane open. -/
def inversePrincipalDomain : Scheme.Opens
    (Proj.basicOpen (grading (equationIdeal F hF))
      (quadraticClass (equationIdeal F hF) Q)).toScheme :=
  originalCubicInverseHom F hF Q hQ R hR ⁻¹ᵁ principalPlaneOpen N

/-- The actual restricted inverse factors through Spec(P_N), not merely
through a point-level parameter set. -/
def inversePrincipalDomainHom :
    (inversePrincipalDomain F hF Q hQ R hR N).toScheme ⟶
      Spec (.of (PlaneLocalization N)) :=
  IsOpenImmersion.lift (principalPlaneι N)
    ((inversePrincipalDomain F hF Q hQ R hR N).ι ≫
      originalCubicInverseHom F hF Q hQ R hR) (by
      rintro _ ⟨z, rfl⟩
      have hz := z.2
      change originalCubicInverseHom F hF Q hQ R hR z.1 ∈ principalPlaneOpen N at hz
      rw [← principalPlaneι_opensRange] at hz
      exact hz)

theorem inversePrincipalDomainHom_fac :
    inversePrincipalDomainHom F hF Q hQ R hR N ≫ principalPlaneι N =
      (inversePrincipalDomain F hF Q hQ R hR N).ι ≫
        originalCubicInverseHom F hF Q hQ R hR :=
  IsOpenImmersion.lift_fac _ _ _

variable (r : Fin 4 → PlanePolynomial k)
variable (hFr : F.eval₂ (algebraMap k (PlanePolynomial k)) r = 0)
variable (a : k) (ha : a ≠ 0)
variable (hQeval : Q.eval₂ (algebraMap k (PlanePolynomial k)) r = C a * N)
variable (hRatios : ∀ i, (R i).eval₂ (algebraMap k (PlanePolynomial k)) r =
  X i * Q.eval₂ (algebraMap k (PlanePolynomial k)) r)

include hRatios in
private theorem forward_range_in_inversePrincipalDomain :
    Set.range (originalCubicForwardPrincipalPlaneHom F hF Q hQ N r hFr a ha hQeval) ⊆
      Set.range (inversePrincipalDomain F hF Q hQ R hR N).ι := by
  rintro _ ⟨z, rfl⟩
  have hpoint := congrArg (fun f => f z)
    (originalCubicForwardPrincipalPlaneHom_inverse F hF Q hQ N r hFr a ha hQeval R hR hRatios)
  change originalCubicInverseHom F hF Q hQ R hR
      (originalCubicForwardPrincipalPlaneHom F hF Q hQ N r hFr a ha hQeval z) =
      principalPlaneι N z at hpoint
  have hz : originalCubicForwardPrincipalPlaneHom F hF Q hQ N r hFr a ha hQeval z ∈
      inversePrincipalDomain F hF Q hQ R hR N := by
    change originalCubicInverseHom F hF Q hQ R hR _ ∈ principalPlaneOpen N
    rw [hpoint, ← principalPlaneι_opensRange]
    exact ⟨z, rfl⟩
  exact ⟨⟨_, hz⟩, rfl⟩

/-- The actual forward map factors into the original inverse-domain open. -/
def originalCubicForwardIntoInverseDomain :
    Spec (.of (PlaneLocalization N)) ⟶
      (inversePrincipalDomain F hF Q hQ R hR N).toScheme :=
  IsOpenImmersion.lift (inversePrincipalDomain F hF Q hQ R hR N).ι
    (originalCubicForwardPrincipalPlaneHom F hF Q hQ N r hFr a ha hQeval)
    (forward_range_in_inversePrincipalDomain F hF Q hQ R hR N r hFr a ha hQeval hRatios)

theorem originalCubicForwardIntoInverseDomain_fac :
    originalCubicForwardIntoInverseDomain F hF Q hQ R hR N r hFr a ha hQeval hRatios ≫
      (inversePrincipalDomain F hF Q hQ R hR N).ι =
      originalCubicForwardPrincipalPlaneHom F hF Q hQ N r hFr a ha hQeval :=
  IsOpenImmersion.lift_fac _ _ _

/-- After both actual restrictions, the first inverse composite is the
identity of the entire principal-plane OPEN SCHEME. -/
theorem originalCubicForwardIntoInverseDomain_inverse :
    originalCubicForwardIntoInverseDomain F hF Q hQ R hR N r hFr a ha hQeval hRatios ≫
      inversePrincipalDomainHom F hF Q hQ R hR N = 𝟙 _ := by
  apply (cancel_mono (principalPlaneι N)).mp
  rw [Category.assoc, inversePrincipalDomainHom_fac,
    ← Category.assoc, originalCubicForwardIntoInverseDomain_fac,
    originalCubicForwardPrincipalPlaneHom_inverse F hF Q hQ N r hFr a ha hQeval R hR hRatios,
    Category.id_comp]

/-- Nonemptiness of the original inverse-domain open is derived by mapping
the generic point of D(N) through the constructed forward map. -/
theorem inversePrincipalDomain_nonempty (hN : N ≠ 0) :
    Nonempty (inversePrincipalDomain F hF Q hQ R hR N).toScheme :=
  Nonempty.map
    (originalCubicForwardIntoInverseDomain F hF Q hQ R hR N r hFr a ha hQeval hRatios)
    (principalPlane_nonempty N hN)

/-- The constructed inverse domain is dense in the SAME original smooth
cubic. Density is internally derived from nonzero N and original smoothness. -/
theorem inversePrincipalDomain_dense_in_original
    (hF0 : F ≠ 0) [Smooth (hypersurfaceToBase F hF)] (hN : N ≠ 0) :
    Dense (((inversePrincipalDomain F hF Q hQ R hR N).ι ≫
      (Proj.basicOpen (grading (equationIdeal F hF))
        (quadraticClass (equationIdeal F hF) Q)).ι).opensRange :
      Set (hypersurface F hF)) := by
  let j := (inversePrincipalDomain F hF Q hQ R hR N).ι ≫
    (Proj.basicOpen (grading (equationIdeal F hF))
      (quadraticClass (equationIdeal F hF) Q)).ι
  letI : Nonempty (inversePrincipalDomain F hF Q hQ R hR N).toScheme :=
    inversePrincipalDomain_nonempty F hF Q hQ R hR N r hFr a ha hQeval hRatios hN
  letI : Nonempty (hypersurface F hF) := Nonempty.map j inferInstance
  letI : IsIntegral (hypersurface F hF) :=
    isIntegral_hypersurface_of_smooth_of_principalIdeal_prime F hF
      (principalIdeal_prime_of_smooth_homogeneous_cubic F hF hF0)
  have hne : (j.opensRange : Set (hypersurface F hF)).Nonempty := by
    obtain ⟨z⟩ := (inferInstance : Nonempty (inversePrincipalDomain F hF Q hQ R hR N).toScheme)
    exact ⟨j z, z, rfl⟩
  exact j.opensRange.isOpen.dense hne

end PfaffianDescent.QuadraticSkewRationality.ForwardChart004
