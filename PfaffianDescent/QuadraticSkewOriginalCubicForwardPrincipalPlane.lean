import PfaffianDescent.QuadraticSkewOriginalCubicForwardChart
/-! SOURCE ONLY / UNVERIFIED. Actual morphisms on the ground principal
affine-plane open D(N), using residual polynomial coordinates. Polynomial
vanishing, denominator, and inverse-numerator identities are the only inputs.
These are intermediate algebra obligations, not final rationality premises. -/

noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.ForwardChart004
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective InverseChart
open scoped AlgebraicGeometry
universe u
variable {k : Type u} [Field k]

abbrev PlanePolynomial (k : Type u) [Field k] := MvPolynomial PlaneIndex.{u} k
abbrev PlaneLocalization (N : PlanePolynomial k) := Localization.Away N

def localizedResidualCoordinates (N : PlanePolynomial k)
    (r : Fin 4 → PlanePolynomial k) : Fin 4 → PlaneLocalization N :=
  fun j => algebraMap (PlanePolynomial k) (PlaneLocalization N) (r j)

theorem localizedResidualCoordinates_eval
    (N : PlanePolynomial k) (r : Fin 4 → PlanePolynomial k)
    (p : MvPolynomial (Fin 4) k) :
    p.eval₂ (algebraMap k (PlaneLocalization N)) (localizedResidualCoordinates N r) =
      algebraMap (PlanePolynomial k) (PlaneLocalization N)
        (p.eval₂ (algebraMap k (PlanePolynomial k)) r) := by
  have h := MvPolynomial.hom_eval₂ p (algebraMap k (PlanePolynomial k))
    (algebraMap (PlanePolynomial k) (PlaneLocalization N)) r
  rw [← IsScalarTower.algebraMap_eq] at h
  exact h.symm

/-- The denominator is internally proved invertible on D(N) from the exact
polynomial residual identity Q(r)=a*N, where a is a nonzero ground scalar. -/
theorem localizedResidualCoordinates_quadratic_isUnit
    (N : PlanePolynomial k) (r : Fin 4 → PlanePolynomial k)
    (Q : MvPolynomial (Fin 4) k) (a : k) (ha : a ≠ 0)
    (hQeval : Q.eval₂ (algebraMap k (PlanePolynomial k)) r = C a * N) :
    IsUnit (Q.eval₂ (algebraMap k (PlaneLocalization N)) (localizedResidualCoordinates N r)) := by
  rw [localizedResidualCoordinates_eval, hQeval, map_mul]
  exact ((isUnit_iff_ne_zero.mpr ha).map
    ((algebraMap (PlanePolynomial k) (PlaneLocalization N)).comp C)).mul
      (IsLocalization.Away.algebraMap_isUnit N)

/-- Standard actual principal-open immersion D(N) into ground affine plane. -/
def principalPlaneι (N : PlanePolynomial k) :
    Spec (.of (PlaneLocalization N)) ⟶ AffineSpace PlaneIndex (Spec (.of k)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (PlanePolynomial k) (PlaneLocalization N))) ≫
      (AffineSpace.SpecIso PlaneIndex (.of k)).inv

instance principalPlaneι_isOpenImmersion (N : PlanePolynomial k) :
    IsOpenImmersion (principalPlaneι N) := by
  unfold principalPlaneι
  infer_instance

/-- The actual ground principal plane open D(N), transported by the canonical
affine-plane polynomial-spectrum isomorphism. -/
def principalPlaneOpen (N : PlanePolynomial k) :
    Scheme.Opens (AffineSpace PlaneIndex (Spec (.of k))) :=
  (AffineSpace.SpecIso PlaneIndex (.of k)).hom ⁻¹ᵁ PrimeSpectrum.basicOpen N

set_option backward.isDefEq.respectTransparency.types false in
theorem principalPlaneι_opensRange (N : PlanePolynomial k) :
    (principalPlaneι N).opensRange = principalPlaneOpen N := by
  unfold principalPlaneι principalPlaneOpen
  rw [Scheme.Hom.opensRange_comp]
  have hRange := @Scheme.Hom.opensRange_localizationAway
    (.of (PlanePolynomial k)) N
  rw [hRange, Scheme.Hom.inv_image]

set_option backward.isDefEq.respectTransparency.types false in
/-- Nonzero N gives density of the actual affine-plane principal open even
over a finite field; the polynomial spectrum's generic point lies in D(N). -/
theorem principalPlaneOpen_dense (N : PlanePolynomial k) (hN : N ≠ 0) :
    Dense (principalPlaneOpen N : Set (AffineSpace PlaneIndex (Spec (.of k)))) := by
  have hne : (PrimeSpectrum.basicOpen N : Set (PrimeSpectrum (PlanePolynomial k))).Nonempty := by
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    change N ∉ (⊥ : Ideal (PlanePolynomial k))
    simpa only [Ideal.mem_bot] using hN
  have hd : Dense (PrimeSpectrum.basicOpen N : Set (PrimeSpectrum (PlanePolynomial k))) :=
    (PrimeSpectrum.basicOpen N).isOpen.dense hne
  unfold principalPlaneOpen
  exact hd.preimage (AffineSpace.SpecIso PlaneIndex (.of k)).hom.homeomorph.isOpenMap

/-- The actual polynomial residual map on D(N) lands in the quadratic open
of the original cubic. No preconstructed scheme map is an input. -/
def originalCubicForwardPrincipalPlaneHom
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2)
    (N : PlanePolynomial k) (r : Fin 4 → PlanePolynomial k)
    (hFr : F.eval₂ (algebraMap k (PlanePolynomial k)) r = 0)
    (a : k) (ha : a ≠ 0)
    (hQeval : Q.eval₂ (algebraMap k (PlanePolynomial k)) r = C a * N) :
    Spec (.of (PlaneLocalization N)) ⟶
      (Proj.basicOpen (grading (equationIdeal F hF))
        (quadraticClass (equationIdeal F hF) Q)).toScheme :=
  originalCubicForwardHom F hF (localizedResidualCoordinates N r)
    (by rw [localizedResidualCoordinates_eval, hFr, map_zero]) Q hQ
    (localizedResidualCoordinates_quadratic_isUnit N r Q a ha hQeval)

/-- The polynomial inverse formulas prove the actual first scheme composite
equals the principal-plane immersion, as an equality of scheme morphisms. -/
theorem originalCubicForwardPrincipalPlaneHom_inverse
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2)
    (N : PlanePolynomial k) (r : Fin 4 → PlanePolynomial k)
    (hFr : F.eval₂ (algebraMap k (PlanePolynomial k)) r = 0)
    (a : k) (ha : a ≠ 0)
    (hQeval : Q.eval₂ (algebraMap k (PlanePolynomial k)) r = C a * N)
    (R : PlaneIndex → MvPolynomial (Fin 4) k) (hR : ∀ i, (R i).IsHomogeneous 2)
    (hRatios : ∀ i, (R i).eval₂ (algebraMap k (PlanePolynomial k)) r =
      X i * Q.eval₂ (algebraMap k (PlanePolynomial k)) r) :
    originalCubicForwardPrincipalPlaneHom F hF Q hQ N r hFr a ha hQeval ≫
      originalCubicInverseHom F hF Q hQ R hR = principalPlaneι N := by
  have hRatiosLocal (i : PlaneIndex) :
      (R i).eval₂ (algebraMap k (PlaneLocalization N)) (localizedResidualCoordinates N r) =
        algebraMap (PlanePolynomial k) (PlaneLocalization N) (X i) *
          Q.eval₂ (algebraMap k (PlaneLocalization N)) (localizedResidualCoordinates N r) := by
    rw [localizedResidualCoordinates_eval, hRatios i, map_mul,
      localizedResidualCoordinates_eval]
  have hpoly : eval₂Hom (algebraMap k (PlaneLocalization N))
      (fun i => algebraMap (PlanePolynomial k) (PlaneLocalization N) (X i)) =
      algebraMap (PlanePolynomial k) (PlaneLocalization N) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      rw [MvPolynomial.eval₂Hom_C]
      exact IsScalarTower.algebraMap_apply k (PlanePolynomial k) (PlaneLocalization N) b
    · intro i
      rw [MvPolynomial.eval₂Hom_X']
  unfold originalCubicForwardPrincipalPlaneHom
  rw [originalCubicForwardHom_inverse _ _ _ _ _ _ _ R hR _ hRatiosLocal, hpoly]
  rfl

/-- Nonzero N makes D(N) an actual nonempty scheme over finite as well as
infinite fields. Its generic point supplies nonemptiness, not a k-point. -/
theorem principalPlane_nonempty (N : PlanePolynomial k) (hN : N ≠ 0) :
    Nonempty (Spec (.of (PlaneLocalization N))) := by
  letI : IsDomain (PlaneLocalization N) := IsLocalization.Away.isDomain (PlaneLocalization N) hN
  infer_instance

end PfaffianDescent.QuadraticSkewRationality.ForwardChart004
